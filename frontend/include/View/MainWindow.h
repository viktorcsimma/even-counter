#ifndef MAINWINDOW_H
#define MAINWINDOW_H

#include <QMainWindow>

#include "ViewModel/MainViewModel.hpp"

QT_BEGIN_NAMESPACE
namespace Ui {
class MainWindow;
}
QT_END_NAMESPACE

class MainWindow : public QMainWindow
{
    Q_OBJECT

public:
    MainWindow(QWidget *parent = nullptr);
    // This does _not_ destruct the view model; that is the task of the main function.
    ~MainWindow();

public slots:
    void addButtonClicked();
    void asyncButtonClicked();
    // Updates the UI according to the current state of the view model.
    // The signal-slot mechanism ensures
    // that this always runs on the main thread
    // when invoked by a signal.
    void updateUI();
    // Makes UI changes
    // when the last iteration of an asynchronous increase finished.
    // Invoked by lastIterationFinished().
    void onLastIterationFinished();
signals:
    // Emitted when an iteration has finished
    // and we wish to display the actual value of the counter.
    void updateRequested();
    // Emitted when the last iteration of an asynchronous increase has finished
    // and we wish to restore the original state of the UI
    // by invoking onLastIterationFinished.
    void lastIterationFinished();

private:
    Ui::MainWindow *ui;

    // The view model behind the window.
    // This refers to the same object throughout the entire existence of the window;
    // mode changes are achieved by changing the HsCalcStateWrapper instance under the view model.
    MainViewModel *viewModel;
};
#endif // MAINWINDOW_H
