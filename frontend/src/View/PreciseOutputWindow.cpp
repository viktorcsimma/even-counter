#include "View/PreciseOutputWindow.h"
#include "View/ui_PreciseOutputWindow.h"
#include "PreciseOutputWindow.moc"

#include <QMovie>

PreciseOutputWindow::PreciseOutputWindow(PreciseOutputViewModel& viewModel, QWidget* parent)
    : QDialog(parent)
    , ui(new Ui::PreciseOutputWindow)  // don't forget! this caused me a lot of segfaults and headaches
    , viewModel(viewModel)
{
    ui->setupUi(this);

#if defined(WIN32) || defined(__APPLE__)
    // Windows and OS X do not use the Button field of the colour palette;
    // so we have to paint the special buttons using stylesheets.
    // But setting the background colour is not too native-feeling here;
    // so let's just give a bold text.
    ui->evaluateButton->setStyleSheet("font-weight: bold; color: unset");
#endif

    // it gets the initial result automatically when the main view model spawns it
    ui->textEdit->setText(QString::fromStdString(viewModel.getResult()));

    ui->spinBox->setValue(viewModel.getPrecision());

    // we set the image for busyIndicatorLabel but hide it
    QSizePolicy sizePolicy = ui->busyIndicatorLabel->sizePolicy(); // for some reason, this cannot be done in a single step
    sizePolicy.setRetainSizeWhenHidden(true); // this way, its place won't be "eaten up" by others if hidden
    ui->busyIndicatorLabel->setSizePolicy(sizePolicy);
    ui->busyIndicatorLabel->setVisible(false);
    //the label itself will be the parent of the movie;
    //this way, we don't have to free it by ourselves
    QMovie* movie = new QMovie("assets/busy_indicator.gif", QByteArray(), ui->busyIndicatorLabel);
    movie->setScaledSize(QSize(26, 26));
    movie->start();
    ui->busyIndicatorLabel->setMovie(movie);

    connect(ui->evaluateButton, &QPushButton::clicked, this, &PreciseOutputWindow::evaluateButtonClicked);
    // we do this in order to ensure that onEvaluationFinished runs in the main thread
    connect(this, &PreciseOutputWindow::evaluationFinished, this, &PreciseOutputWindow::onEvaluationFinished);

    // and put the spinbox into focus so that we can start giving the precision
    ui->spinBox->setFocus();
}

PreciseOutputWindow::~PreciseOutputWindow() {
    viewModel.interruptEvaluation();
}

void PreciseOutputWindow::evaluateButtonClicked()
{
    if ("Evaluate" == ui->evaluateButton->text()) startEvaluation();
    else interruptEvaluation();
}

void PreciseOutputWindow::enterKeyPressed()
{
    if ("Evaluate" == ui->evaluateButton->text()) startEvaluation();
    // else do nothing
}

void PreciseOutputWindow::onEvaluationFinished()
{
    std::string result = viewModel.getResult();
    if (result.find("interrupted") == result.npos) { // that means it does not contain that
        ui->textEdit->setText(QString::fromStdString(viewModel.getResult()));
    } else {
        ui->textEdit->setText("Interrupted.\nChoose a new precision and click \"Evaluate\" again.");
    }
    ui->evaluateButton->setText("Evaluate");
    ui->evaluateButton->setEnabled(true);
    ui->busyIndicatorLabel->setVisible(false);
}

void PreciseOutputWindow::startEvaluation()
{
    viewModel.setPrecisionAsync(ui->spinBox->value(), [this]() {emit evaluationFinished();});
    ui->evaluateButton->setText("Cancel");
    ui->busyIndicatorLabel->setVisible(true);
}

void PreciseOutputWindow::interruptEvaluation()
{
    ui->evaluateButton->setEnabled(false);
    viewModel.interruptEvaluation();
}

