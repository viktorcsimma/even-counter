#include "View/HistoryItemWidget.h"
#include "View/ui_HistoryItemWidget.h"

HistoryItemWidget::HistoryItemWidget(int id, const QString& command, const QString& result, QWidget* parent)
    : QFrame(parent)
    , ui(new Ui::HistoryItemWidget)
    , id(id)
{
    ui->setupUi(this);

    ui->commandLabel->setText(command);
    ui->resultLabel->setText(result);
}

void HistoryItemWidget::mouseReleaseEvent(QMouseEvent* event) {
    emit clicked();
}
